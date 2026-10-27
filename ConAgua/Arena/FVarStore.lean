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
# The expression `fvar` node store in L: a `Nat` field and a handle field per node

The arena's expression store keeps `fvar idx ty` nodes in a `Tbl FVarNode EIdx UInt64` per tier
(`Arena/Store.lean:258`, `ETables.fvars`). Its L representation is `app`'s shape (two words per
node, open addressing, scratch-skipping), except the first word is a plain `Nat` (the free
variable index, as `bvar`'s word is) rather than a handle:

* **Records.** Word array `FVREC`, two words per node (the index `idx` as a word, then the handle
  word of `ty`), tiers interleaved: node `i` of tier `t` at `FVREC[4 i + 2 t ..]`. The node count
  of tier `t` is `CTL[26 + t]`.
* **Cons table.** Word array `FVSLOT`, the same open addressing as `SLOT`/`ASLOT`.
* **The scratch skip.** `internE (.fvar idx ty)` does not probe the persistent tier when the
  scratch tier is open and `ty` is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild (.fvar _ ty) = !ty.isPersistent`): only the `ty` word, not `idx`, the
  index not being a handle at all.

The functions: `fvar_find(t, u, ty, h)` (the probe, the match inline: a word comparison and a
handle-word comparison), `fvar_push(t, u, ty, j)` and `intern_fvar(u, ty)`. They are the cons-table library's templates
(`ConsLib.lean`) at the schema `fvarCS`, the derived column written by the template's prelude;
their specs are the library's (`ConsLibSpec.lean`) from this table's obligations.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The hash of an `fvar` record (FNV-1a over its two words). -/
def fvarHashW (u ty : Word) : Word := ((fnvBasis ^^^ u) * fnvPrime ^^^ ty) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(u, ty)` (the index word, the child's handle
word). -/
def fvmatchW (r : Array Word) (_t i u ty : Word) : Bool :=
  rdW r (i * 2) == u && rdW r (i * 2 + 1) == ty

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `fvar` tier (tag `1`). -/
def fvarP : Word := 0x10000000
def fvarS : Word := 0x18000000

/-- The hash of node `i` of tier `t`. -/
def fvhash (m : Mem) (t i : Word) : Word :=
  fvarHashW (rdW (m.arr64 (tierA FVREC t)) (i * 2)) (rdW (m.arr64 (tierA FVREC t)) (i * 2 + 1))

/-- The `fvar` table as a cons schema (`ConsLib.lean`); the derived column `FVLP`
(the type's `lp` bit, `lpBlkF`). -/
def fvarCS : ConsSch where
  ra := FVREC
  sa := FVSLOT
  w := 2
  ca := 26
  P := fvarP
  S := fvarS
  tag := 1
  fname := "fvar_find"
  pname := "fvar_push"
  nk := 2
  exact := true
  mc := condOf (lblk (t, u, ty, h, n, j, d, v, b) {
    if FVREC⟨t⟩[(v - 1) * 2] == u && FVREC⟨t⟩[(v - 1) * 2 + 1] == ty { skip } })
  np := 2
  room := condOf (lblk (t, u, ty, j, c) {
    if len(FVREC⟨t⟩) >> 1 <= c || len(FVLP⟨t⟩) <= c { skip } })
  recW := [.var 1, .var 2]
  ihash := lblk (u, ty, h) { h := ((⟪fnvBasis⟫ ^ u) * ⟪fnvPrime⟫ ^ ty) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (u, ty, h, sk) { sk := (ty >> 27) & 1 }))
  xloc := 4
  pre := some lpBlkF
  col := some FVLP
  colM m as := exprLPW m (as.getD 1 0)
  mtM m ks t i := fvmatchW (m.arr64 (tierA FVREC t)) t i (ks.getD 0 0) (ks.getD 1 0)
  qhM _ ks := fvarHashW (ks.getD 0 0) (ks.getD 1 0)
  hsM := fvhash
  vsM as := as
  roomM m t c := decide (m.len64 (tierA FVREC t) >>> (1 : Word) ≤ c) || decide (m.len64 (tierA FVLP t) ≤ c)
  skM ks := (ks.getD 1 0 >>> 27) &&& 1

/-! ## `fvar_find(t, u, ty, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def fvarFind : FunDecl := consFindG fvarCS

/-! ## `fvar_push(t, u, ty, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `fvar` table, `CTL[26 + t]`. -/
def fvcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (26 + t)

/-- `fvar_push`'s room checks: the handle index, the record array. -/
def fvpushOK (m : Mem) (t : Word) : Bool :=
  decide (fvcnt m t < (134217728 : Word)) && decide (fvcnt m t < m.len64 (tierA FVREC t) >>> (1 : Word)) &&
    decide (fvcnt m t < m.len64 (tierA FVLP t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def fvarPush : FunDecl := consPushG fvarCS

/-! ## `intern_fvar(u, ty)`: hash-cons the expression `fvar u ty`

con-ron's `EStore::intern` at `fvar` and the arena's `internE (.fvar u.toNat ty)`: the persistent
probe unless the scratch tier is open and `ty` is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. -/

/-- The scratch skip: the scratch tier is open and `ty` is a scratch handle. The index `u` is not
a handle, so only `ty` is tested. -/
def fvskipW (m : Mem) (ty : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then (ty >>> 27) &&& 1 else 0

/-- The model of `intern_fvar`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def fvinternW (m : Mem) (u ty : Word) : Option (Word × Mem) := consInternM fvarCS m [u, ty]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internFVar : FunDecl := consInternG fvarCS

/-- The `fvar` store functions, as one `#eval`-able program. -/
def fvarProg : Prog :=
  [("fvar_find", fvarFind), ("fvar_push", fvarPush), ("intern_fvar", internFVar)]

/-- A memory with 8 `fvar` nodes and `SN0` slots per tier, the scratch tier closed or open. Arrays
0‥24 (the other tables') are unused here and left empty. -/
def fvarMem (scratch : Word) : Mem :=
  { words := withTiers <| (Array.replicate 25 #[]).set! 1 ((Array.replicate 64 0).set! 1 scratch) ++
      #[Array.replicate consTestWords 0, Array.replicate consTestWords 0] ++ Array.replicate 62 (Array.replicate consTestWords 0) }

/-- Intern each `(index, ty)` pair in turn; the handles. -/
def internFVars (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (u, ty) :: xs => match run fvarProg 100 "intern_fvar" [u, ty] m with
    | .ok (r, m') => (internFVars m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `fvar 0 1`, `fvar 1 1`, `fvar 0 2`, `fvar 0 1`: persistent handles 0, 1, 2, 0 (sharing is on the
whole pair, not the index alone or the type alone). -/
#guard internFVars (fvarMem 0) [(0, 1), (1, 1), (0, 2), (0, 1)] ==
  some [0x10000000, 0x10000001, 0x10000002, 0x10000000]

/- Scratch open: a persistent `ty` is probed in the persistent tier (empty); the nodes go to the
scratch tier; a scratch `ty` (`0x08000000`) skips the persistent probe. -/
#guard internFVars (fvarMem 1) [(0, 1), (0, 0x08000000), (0, 1), (0, 0x08000000)] ==
  some [0x18000000, 0x18000001, 0x18000000, 0x18000001]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `fvar` table's obligations.** -/
theorem fvarOK : ConsOK p fvarCS where
  match_ := by
    intro s
    simp [fvarCS, condOf, Cond.pval, Expr.pval, fvmatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ]
  ihash := by
    intro n s₀
    simp only [fvarCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, fvarHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, fvarCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, fvarHashW, argsOf, BinOp.eval]
  pre := by
    intro n s₀
    vcgen [lpBlkF_spec p (exec p n) s₀]
    all_goals obtain ⟨h0, h1, h2, h3, -, -, hx⟩ := ‹_ ∧ _›
    · assumption
    · intro x hx'
      simp only [fvarCS] at hx'
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl <;> assumption
    · simp [fvarCS, argsOf, List.range_succ, hx]
  colA := by
    intro A h
    simp only [fvarCS, Option.some.injEq] at h
    subst h; decide
  recs := ⟨by
      intro e he s s' h
      simp only [fvarCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [fvarCS, argsOf, Expr.pval, List.range_succ]⟩
  room := fun s => by
    simp only [fvarCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by
    intro e he s
    simp only [fvarCS, Option.some.injEq] at he
    subst he
    simp [fvarCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [fvarCS, Option.some.injEq] at h; (try subst h); (try decide)⟩
  qpure := fun h => by simp [fvarCS] at h
  mloc := fun h => by simp [fvarCS] at h
  exnk := fun _ => by decide

theorem fvpushOK_eqC (m : Mem) (t : Word) : fvpushOK m t = pushOKC fvarCS m t := by
  simp only [fvpushOK, pushOKC, fvarCS, Bool.not_or, ← decide_not, UInt64.not_le, Bool.and_assoc]
  rfl

theorem internFVar_spec (hpf : p.lookup "fvar_find" = some fvarFind)
    (hpp : p.lookup "fvar_push" = some fvarPush) (hp : p.lookup "intern_fvar" = some internFVar)
    (n : Nat) (s₀ : St) (u ty : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_fvar" [u, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ fvinternW s₀.mem u ty = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p fvarCS (fvarOK p) hpf hpp "intern_fvar" hp n s₀ [u, ty] rfl trivial

end specs

end L.Arena
