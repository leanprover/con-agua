module

public import ConAgua.Arena.Store
public import ConAgua.Arena.LpCol
public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.Arena.LpCol
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
import ConAgua.Census.Attr

@[expose] public section

/-!
# The expression `sort` node store in L: a store with a scratch skip, one handle field

The arena's expression store keeps `sort u` nodes in a `Tbl SortNode EIdx UInt64` per tier
(`Arena/Store.lean:278`, `ETables.sorts`). Its L representation is the `succ` store's shape
(`LevelStore.lean`: one handle field) but, like `app`, with the expression store's scratch skip:
`internE (.sort u)` does not probe the persistent tier when the scratch tier is open and `u` is a
scratch handle (`EStore.persFindMaybe`, `eViewHasScratchChild (.sort u) = !u.isPersistent`).

* **Records.** Word array `SOREC`, one word per node (the handle word of `u`), tiers interleaved:
  node `i` of tier `t` at `SOREC[2 i + t]`. The node count of tier `t` is `CTL[16 + t]`.
* **Cons table.** Word array `SOSLOT`, the same open addressing as `SLOT`.

The functions: `sort_find(t, u, h)`, `sort_push(t, u, j)` and `intern_sort(u)`. They are the cons-table library's templates
(`ConsLib.lean`) at the schema `sortCS`, the derived column written by the template's prelude;
their specs are the library's (`ConsLibSpec.lean`) from this table's obligations.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `sort` records, both tiers interleaved (one word per node). -/
abbrev SOREC : ArrId := 16
/-- The `sort` cons-table slots, both tiers interleaved. -/
abbrev SOSLOT : ArrId := 17

/-- The hash of a `sort` record (FNV-1a over its word). -/
def sortHashW (u : Word) : Word := (fnvBasis ^^^ u) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `sort u`. -/
def somatchW (r : Array Word) (_t i u : Word) : Bool := rdW r i == u

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `sort` tier (tag `2`). -/
def sortP : Word := 0x20000000
def sortS : Word := 0x28000000

/-- The hash of node `i` of tier `t`. -/
def sohash (m : Mem) (t i : Word) : Word := sortHashW (rdW (m.arr64 (tierA SOREC t)) i)

/-- The column's prelude in the template's layout (`hpBlkS` with the push's `k` inserted before
`x`): `x := lvlHP(u)`. -/
def soPre : Stmt := mapS (fun v => if v < 4 then v else v + 1) hpBlkS

/-- The `sort` table as a cons schema (`ConsLib.lean`); the derived column `SOLP`
(the level's `hasParam` bit, `hpBlkS`). -/
def sortCS : ConsSch where
  ra := SOREC
  sa := SOSLOT
  w := 1
  ca := 16
  P := sortP
  S := sortS
  tag := 2
  fname := "sort_find"
  pname := "sort_push"
  nk := 1
  exact := true
  mc := condOf (lblk (t, u, h, n, j, d, v, b) {
    if SOREC⟨t⟩[(v - 1)] == u { skip } })
  np := 1
  room := condOf (lblk (t, u, j, c) {
    if len(SOREC⟨t⟩) <= c || len(SOLP⟨t⟩) <= c { skip } })
  recW := [.var 1]
  ihash := lblk (u, h) { h := (⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (u, h, sk) { sk := (u >> 27) & 1 }))
  xloc := 4
  pre := some soPre
  col := some SOLP
  colM m as := lvlHPW m (as.getD 0 0)
  mtM m ks t i := somatchW (m.arr64 (tierA SOREC t)) t i (ks.getD 0 0)
  qhM _ ks := sortHashW (ks.getD 0 0)
  hsM := sohash
  vsM as := as
  roomM m t c := decide (m.len64 (tierA SOREC t) ≤ c) || decide (m.len64 (tierA SOLP t) ≤ c)
  skM ks := (ks.getD 0 0 >>> 27) &&& 1

/-! ## `sort_find(t, u, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def sortFind : FunDecl := consFindG sortCS

/-! ## `sort_push(t, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `sort` table, `CTL[16 + t]`. -/
def socnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (16 + t)

/-- `sort_push`'s room checks: the handle index, the record array. -/
def sopushOK (m : Mem) (t : Word) : Bool :=
  decide (socnt m t < (134217728 : Word)) && decide (socnt m t < m.len64 (tierA SOREC t)) &&
    decide (socnt m t < m.len64 (tierA SOLP t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def sortPush : FunDecl := consPushG sortCS

/-! ## `intern_sort(u)`: hash-cons the expression `sort u`

con-ron's `EStore::intern` at `sort` and the arena's `internE (.sort u)`: the persistent probe
unless the scratch tier is open and `u` is a scratch handle, the scratch probe if the scratch
tier is open, the append to the tier the store is in. -/

/-- The scratch skip: the scratch tier is open and `u` is a scratch handle. -/
def soskipW (m : Mem) (u : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then (u >>> 27) &&& 1 else 0

/-- The model of `intern_sort`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def sointernW (m : Mem) (u : Word) : Option (Word × Mem) := consInternM sortCS m [u]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internSort : FunDecl := consInternG sortCS

/-- The `sort` store functions, as one `#eval`-able program. -/
def sortProg : Prog :=
  [("sort_find", sortFind), ("sort_push", sortPush), ("intern_sort", internSort)]

/-- A memory with 8 `sort` nodes and `SN0` slots per tier, the scratch tier closed or open. Arrays
0‥15 (the other tables') are unused here and left empty. -/
def sortMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], Array.replicate 16 0,
      Array.replicate consTestWords 0] ++ Array.replicate 44 (Array.replicate consTestWords 0) }

/-- Intern each handle word in turn; the handles. -/
def internSorts (m : Mem) : List Word → Option (List Word)
  | [] => some []
  | u :: xs => match run sortProg 100 "intern_sort" [u] m with
    | .ok (r, m') => (internSorts m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `sort` of handles `1`, `2`, `1`: persistent handles 0, 1, 0 (sharing). -/
#guard internSorts (sortMem 0) [1, 2, 1] == some [0x20000000, 0x20000001, 0x20000000]

/- Scratch open: a persistent child is probed in the persistent tier (empty); the nodes go to
the scratch tier; a scratch child (`0x28000000`) skips the persistent probe. -/
#guard internSorts (sortMem 1) [1, 0x28000000, 1, 0x28000000] ==
  some [0x28000000, 0x28000001, 0x28000000, 0x28000001]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

theorem soPre_spec (k : Stmt → M Sig) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k soPre
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 5 = lvlHPW s₀.mem (s₀.loc 1); ⊤⦄ := by
  simp only [soPre, hpBlkS, mapS, mapE_tld, mapE_cntE, mapE_tierE, mapE_idxE, mapE, mapC, L.Notation.blk]
  simp only [Nat.reduceLT, Nat.reduceAdd, ↓reduceIte]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [lvlHPW, tierW, idxW]

/-- **The `sort` table's obligations.** -/
theorem sortOK : ConsOK p sortCS where
  match_ := by
    intro s
    simp [sortCS, condOf, Cond.pval, Expr.pval, somatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [sortCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, sortHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, sortCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, sortHashW, argsOf, BinOp.eval]
  pre := by
    intro n s₀
    vcgen [soPre_spec p (exec p n) s₀]
    all_goals obtain ⟨h0, h1, h2, hx⟩ := ‹_ ∧ _›
    · assumption
    · intro x hx'
      simp only [sortCS] at hx'
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2) with rfl | rfl | rfl <;> assumption
    · simp [sortCS, argsOf, List.range_succ, hx]
  colA := by
    intro A h
    simp only [sortCS, Option.some.injEq] at h
    subst h; decide
  recs := ⟨by
      intro e he s s' h
      simp only [sortCS, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; simp [Expr.pval, h],
    fun s => by simp [sortCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [sortCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by
    intro e he s
    simp only [sortCS, Option.some.injEq] at he
    subst he
    simp [sortCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [sortCS, reduceCtorEq, Option.some.injEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [sortCS] at h
  mloc := fun h => by simp [sortCS] at h
  exnk := fun _ => by decide

theorem sopushOK_eqC (m : Mem) (t : Word) : sopushOK m t = pushOKC sortCS m t := by
  simp only [sopushOK, pushOKC, sortCS, Bool.not_or, ← decide_not, UInt64.not_le, Bool.and_assoc]
  rfl

theorem internSort_spec (hpf : p.lookup "sort_find" = some sortFind)
    (hpp : p.lookup "sort_push" = some sortPush) (hp : p.lookup "intern_sort" = some internSort)
    (n : Nat) (s₀ : St) (u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_sort" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ sointernW s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p sortCS (sortOK p) hpf hpp "intern_sort" hp n s₀ [u] rfl trivial

end specs

end L.Arena
