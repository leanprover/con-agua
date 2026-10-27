module

public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
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

The functions `param_find(t, u, h)`, `param_push(t, u, j)` and `intern_param(u)` are the
cons-table library's templates (`ConsLib.lean`) at the schema `paramCS` (no scratch skip); their
specs are the library's (`ConsLibSpec.lean`) from this table's obligations (`paramOK`).
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
def pmatchW (r : Array Word) (_t i u : Word) : Bool := rdW r i == u

/-- The hash of node `i` of tier `t`. -/
def phash (m : Mem) (t i : Word) : Word := paramHashW (rdW (m.arr64 (tierA PREC t)) i)

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `param` tier (tag `4`). -/
def paramP : Word := 0x40000000
def paramS : Word := 0x48000000

/-- The `param` table as a cons schema: one key word, stored as the record; the match is one word comparison;
no scratch skip. -/
def paramCS : ConsSch where
  ra := PREC
  sa := PSLOT
  w := 1
  ca := 14
  P := paramP
  S := paramS
  tag := 4
  fname := "param_find"
  pname := "param_push"
  nk := 1
  exact := true
  mc := condOf (lblk (t, u, h, n, j, d, v, b) { if PREC⟨t⟩[(v - 1)] == u { skip } })
  np := 1
  room := condOf (lblk (t, u, j, c) { if len(PREC⟨t⟩) <= c { skip } })
  recW := [.var 1]
  ihash := lblk (u, h) { h := (⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ }
  skipW := none
  mtM m ks t i := pmatchW (m.arr64 (tierA PREC t)) t i (ks.getD 0 0)
  qhM _ ks := paramHashW (ks.getD 0 0)
  hsM := phash
  vsM as := as
  roomM m t c := decide (m.len64 (tierA PREC t) ≤ c)

/-! ## `param_find(t, u, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def paramFind : FunDecl := consFindG paramCS

/-! ## `param_push(t, u, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `param` table, `CTL[14 + t]`. -/
def pcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (14 + t)

/-- `param_push`'s room checks: the handle index, the record array. -/
def ppushOK (m : Mem) (t : Word) : Bool :=
  decide (pcnt m t < (134217728 : Word)) && decide (pcnt m t < m.len64 (tierA PREC t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def paramPush : FunDecl := consPushG paramCS

/-! ## `intern_param(u)`: hash-cons the level `param n`

con-ron's `LStore::intern` at `param` and the arena's `internLNode (.param n)`: the persistent
probe, the scratch probe if the scratch tier is open, the append to the tier the store is in. -/

/-- The model of `intern_param`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def pinternW (m : Mem) (u : Word) : Option (Word × Mem) := consInternM paramCS m [u]

/-- con-ron: ConRon/Arena/Monad.lean:441-457 ConRon.Arena.internLNode -/
@[l_impl ConRon.Arena.internLNode]
def internParam : FunDecl := consInternG paramCS

/-- The `param` store functions, as one `#eval`-able program. -/
def paramProg : Prog :=
  [("param_find", paramFind), ("param_push", paramPush), ("intern_param", internParam)]

/-- A memory with 8 `param` nodes and `SN0` slots per tier, the scratch tier closed or open. Arrays
0‥13 (the other tables' `REC`/`SLOT` arrays) are unused here and left empty. -/
def paramMem (scratch : Word) : Mem :=
  { words := withTiers <| #[#[], (#[0, scratch] ++ Array.replicate 62 0), #[], #[], #[], #[],
      #[], #[], #[], #[], #[], #[], #[], #[], Array.replicate 16 0, Array.replicate consTestWords 0] }

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

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `param` table's obligations.** -/
theorem paramOK : ConsOK p paramCS where
  match_ := by
    intro s
    simp [paramCS, condOf, Cond.pval, Expr.pval, pmatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [paramCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, paramHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, paramCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, paramHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [paramCS, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; simp [Expr.pval, h],
    fun s => by simp [paramCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [paramCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval]; rfl
  skips := by intro e he; simp [paramCS] at he
  pre := rfl
  colA := by simp [paramCS]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [paramCS, reduceCtorEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [paramCS] at h
  mloc := fun h => by simp [paramCS] at h
  exnk := fun _ => by decide

theorem ppushOK_eqC (m : Mem) (t : Word) : ppushOK m t = pushOKC paramCS m t := by
  simp only [ppushOK, pushOKC, pcnt, cntC, paramCS, ← decide_not, UInt64.not_le]; rfl

theorem internParam_spec (hpf : p.lookup "param_find" = some paramFind)
    (hpp : p.lookup "param_push" = some paramPush) (hp : p.lookup "intern_param" = some internParam)
    (n : Nat) (s₀ : St) (u : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_param" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ pinternW s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p paramCS (paramOK p) hpf hpp "intern_param" hp n s₀ [u] rfl trivial

end specs

end L.Arena
