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

@[expose] public section

/-!
# The expression `proj` node store in L: two handle fields and a `Nat` field per node

The arena's expression store keeps `proj n i e` nodes in a `Tbl ProjNode EIdx UInt64` per tier
(`Arena/Store.lean:308`, `ETables.projs`). Its L representation is `letE`'s shape (three words per
node, open addressing, scratch-skipping), except the middle word is a plain `Nat` (the projection
index, as `bvar`'s word is) rather than a handle:

* **Records.** Word array `PJREC`, two words per node (the name handle word `n` and the
  expression handle word `e` packed, `n | e << 32`, then the index `i` as a word), one array per tier: node `i` of tier `t` at
  `PJREC⟨t⟩[2 i ..]`. The node count of tier `t` is `CTL[32 + t]`.
* **Cons table.** Word array `PJSLOT`, the same open addressing as `SLOT`/`LESLOT`.
* **The scratch skip.** `internE (.proj n i e)` does not probe the persistent tier when the
  scratch tier is open and `n` or `e` is a scratch handle (`EStore.persFindMaybe`,
  `eViewHasScratchChild (.proj n _ e) = if n.isPersistent then !e.isPersistent else true`): bit 27
  of `n | e`, the index `i` not being a handle at all. `letE`'s record width (3) is not a power of
  two, so (as for `letE`) the record-room check is stated by multiplication, not a shift: `L` has
  no division (`PLAN.md`, "the language L").

The functions `proj_find(t, n, u, e, h)` (the probe, the match inline: two handle-word
comparisons and a word comparison), `proj_push(t, n, u, e, j)` and `intern_proj(n, u, e)` are
the cons-table library's templates (`ConsLib.lean`) at the schema `projCS`; their specs are the
library's (`ConsLibSpec.lean`) from this table's obligations (`projOK`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `proj` records, both tiers interleaved (two words per node). -/
abbrev PJREC : ArrId := 31
/-- The `proj` cons-table slots, both tiers interleaved. -/
abbrev PJSLOT : ArrId := 32

/-- The hash of a `proj` record (FNV-1a over its three fields). -/
def projHashW (n u e : Word) : Word :=
  (((fnvBasis ^^^ n) * fnvPrime ^^^ u) * fnvPrime ^^^ e) * fnvPrime

/-- The model of the match: node `i` of tier `t` is `(n, u, e)`. -/
def pjmatchW (r : Array Word) (_t i n u e : Word) : Bool :=
  rdW r (i * 2) &&& 4294967295 == n && rdW r (i * 2 + 1) == u && rdW r (i * 2) >>> 32 == e

/-- The hash of node `i` of tier `t`. -/
def pjhash (m : Mem) (t i : Word) : Word :=
  projHashW (rdW (m.arr64 (tierA PJREC t)) (i * 2) &&& 4294967295) (rdW (m.arr64 (tierA PJREC t)) (i * 2 + 1))
    (rdW (m.arr64 (tierA PJREC t)) (i * 2) >>> 32)

/-! ## The schema -/

/-- The handle word of node `0` of the persistent / scratch `proj` tier (tag `9`). -/
def projP : Word := 0x90000000
def projS : Word := 0x98000000

/-- The `proj` table as a cons schema: three key words `n u e`, packed into the record; the match
is three field comparisons; the scratch skip is bit 27 of `n | e` (the index `u` is not a handle). -/
def projCS : ConsSch where
  ra := PJREC
  sa := PJSLOT
  w := 2
  ca := 32
  P := projP
  S := projS
  tag := 9
  fname := "proj_find"
  pname := "proj_push"
  nk := 3
  mc := condOf (lblk (t, n, u, e, h, nn, j, d, w, b) {
    if (PJREC⟨t⟩[(w - 1) * 2] & 4294967295) == n && PJREC⟨t⟩[(w - 1) * 2 + 1] == u
        && (PJREC⟨t⟩[(w - 1) * 2] >> 32) == e { skip } })
  np := 3
  room := condOf (lblk (t, n, u, e, j, c) { if len(PJREC⟨t⟩) < (c + 1) * 2 { skip } })
  recW := [.bin .or (.var 1) (.bin .shl (.var 3) (.const 32)), .var 2]
  ihash := lblk (n, u, e, h) {
    h := (((⟪fnvBasis⟫ ^ n) * ⟪fnvPrime⟫ ^ u) * ⟪fnvPrime⟫ ^ e) * ⟪fnvPrime⟫ }
  skipW := some (rhsOf (lblk (n, u, e, h, sk) { sk := ((n | e) >> 27) & 1 }))
  mtM m ks t i := pjmatchW (m.arr64 (tierA PJREC t)) t i (ks.getD 0 0) (ks.getD 1 0) (ks.getD 2 0)
  qhM _ ks := projHashW (ks.getD 0 0) (ks.getD 1 0) (ks.getD 2 0)
  hsM := pjhash
  vsM as := [as.getD 0 0 ||| as.getD 2 0 <<< 32, as.getD 1 0]
  roomM m t c := decide (m.len64 (tierA PJREC t) < (c + 1) * 2)
  skM ks := ((ks.getD 0 0 ||| ks.getD 2 0) >>> 27) &&& 1

/-! ## `proj_find(t, n, u, e, h)`: the probe -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def projFind : FunDecl := consFindG projCS

/-! ## `proj_push(t, n, u, e, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The node count of tier `t` of the `proj` table, `CTL[32 + t]`. -/
def pjcnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (32 + t)

/-- `proj_push`'s room checks: the handle index, the record array, the load limit. `PJREC`'s
width (3) is not a power of two, so (as for `letE`) the record-room check is stated by
multiplication, `(c + 1) * 6 ≤ len`, matching `PushRoom`'s own shape directly (`L` has no
division). -/
def pjpushOK (m : Mem) (t : Word) : Bool :=
  decide (pjcnt m t < (134217728 : Word)) && decide ((pjcnt m t + 1) * 2 ≤ m.len64 (tierA PJREC t))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def projPush : FunDecl := consPushG projCS

/-! ## `intern_proj(n, u, e)`: hash-cons the expression `proj n u e`

con-ron's `EStore::intern` at `proj` and the arena's `internE (.proj n u.toNat e)`: the persistent
probe unless the scratch tier is open and `n` or `e` is a scratch handle, the scratch probe if the
scratch tier is open, the append to the tier the store is in. -/

/-- The scratch skip: the scratch tier is open and `n` or `e` is a scratch handle. The index `u`
is not a handle, so it is not tested. -/
def pjskipW (m : Mem) (n e : Word) : Word :=
  if rdW (m.arr64 CTL) 1 ≠ 0 then ((n ||| e) >>> 27) &&& 1 else 0

/-- The model of `intern_proj`: the handle and the memory after, or `none` where the L code
aborts (the library's `consInternM`). -/
def pjinternW (m : Mem) (n u e : Word) : Option (Word × Mem) := consInternM projCS m [n, u, e]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internProj : FunDecl := consInternG projCS

/-- The `proj` store functions, as one `#eval`-able program. -/
def projProg : Prog :=
  [("proj_find", projFind), ("proj_push", projPush), ("intern_proj", internProj)]

/-- A memory with 8 `proj` nodes and `SN0` slots per tier, the scratch tier closed or open. Arrays
0‥30 (the other tables') are unused here and left empty. -/
def projMem (scratch : Word) : Mem :=
  { words := withTiers <| (Array.replicate 31 #[]).set! 1 ((Array.replicate 64 0).set! 1 scratch) ++
      #[Array.replicate 48 0, Array.replicate consTestWords 0] }

/-- Intern each `(n, i, e)` triple in turn; the handles. -/
def internProjs (m : Mem) : List (Word × Word × Word) → Option (List Word)
  | [] => some []
  | (n, u, e) :: xs => match run projProg 100 "intern_proj" [n, u, e] m with
    | .ok (r, m') => (internProjs m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `proj 1 0 2`, `proj 2 0 1`, `proj 1 1 2`, `proj 1 0 2`: persistent handles 0, 1, 2, 0 (sharing
is on the whole triple, not any one field). -/
#guard internProjs (projMem 0) [(1, 0, 2), (2, 0, 1), (1, 1, 2), (1, 0, 2)] ==
  some [0x90000000, 0x90000001, 0x90000002, 0x90000000]

/- Scratch open: a scratch `e` (`0x98000000`) skips the persistent probe; the index `u` alone
being a bit-27 word does not (it is not tested). -/
#guard internProjs (projMem 1) [(1, 0, 2), (1, 0, 0x98000000), (1, 0, 2), (1, 0, 0x98000000)] ==
  some [0x98000000, 0x98000001, 0x98000000, 0x98000001]

/-! ## The specs: the library's, from this table's obligations -/

section specs
variable (p : Prog)

/-- **The `proj` table's obligations.** -/
theorem projOK : ConsOK p projCS where
  match_ := by
    intro s
    simp [projCS, condOf, Cond.pval, Expr.pval, pjmatchW, argsOf, rd64_rdWC, L.Notation.blk,
      Cmp.eval, BinOp.eval, List.range_succ, Bool.and_assoc]
  ihash := by
    intro n s₀
    simp only [projCS, L.Notation.blk]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, projHashW, argsOf, BinOp.eval]
  ihashG := fun _ => by
    intro n s₀
    simp only [ihashAt, projCS, gO, shiftS, shiftE, L.Notation.blk, Nat.reduceAdd]
    vcgen [step, evalE_spec, setLoc]
    all_goals simp_all [Expr.pval, projHashW, argsOf, BinOp.eval]
  recs := ⟨by
      intro e he s s' h
      simp only [projCS, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [projCS, argsOf, Expr.pval, BinOp.eval, List.range_succ]⟩
  room := fun s => by
    simp only [projCS, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl
  skips := by
    intro e he s
    simp only [projCS, Option.some.injEq] at he
    subst he
    simp [projCS, rhsOf, L.Notation.blk, Expr.pval, argsOf, BinOp.eval, List.range_succ]
  pre := rfl
  colA := by simp [projCS]
  push_np := by decide
  arrs := by decide
  lt := ⟨by decide, by decide, fun A h => by
    simp only [projCS, reduceCtorEq] at h; (try subst h); (try decide)⟩
  qpure := fun _ _ _ _ _ => rfl
  mloc := fun h => by simp [projCS] at h
  exnk := fun h => by simp [projCS] at h

theorem pjpushOK_eqC (m : Mem) (t : Word) : pjpushOK m t = pushOKC projCS m t := by
  simp only [pjpushOK, pushOKC, projCS, pjcnt, cntC, ← decide_not, UInt64.not_lt]; rfl

theorem internProj_spec (hpf : p.lookup "proj_find" = some projFind)
    (hpp : p.lookup "proj_push" = some projPush) (hp : p.lookup "intern_proj" = some internProj)
    (nn : Nat) (s₀ : St) (n u e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p nn) "intern_proj" [n, u, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pjinternW s₀.mem n u e = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p projCS (projOK p) hpf hpp "intern_proj" hp nn s₀ [n, u, e] rfl trivial

end specs

end L.Arena
